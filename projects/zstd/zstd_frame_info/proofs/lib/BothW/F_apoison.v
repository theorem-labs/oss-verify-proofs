(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase F_memset.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition poison_entry := 0x52f74%Z.

(* [comment removed for export] *)
Definition poison_cells (m : amem) : Prop :=
     rw_cells bsegs m 0x99000 [C8 (Z_to_bv 64 0x132b68); C8 (Z_to_bv 64 0x9e838); C8 (Z_to_bv 64 0xa1038);
                               C8 (Z_to_bv 64 0xa1d28); C8 (Z_to_bv 64 0xa1d30); C8 (Z_to_bv 64 0xa1d20)]
  /\ rw_cells bsegs m 0x99030 [C8 (Z_to_bv 64 0x9ae98)]
  /\ rw_cells bsegs m 0x9ae90 [C8 (Z_to_bv 64 0x92340); C8 (Z_to_bv 64 0x92744)]
  /\ rw_cells bsegs m 0xa1038 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells bsegs m 0xa1d20 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0xa089c [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x132be0 [C8 (Z_to_bv 64 0xffffffffffffffff)].

#[using="Type"] Lemma poison_cells_frame : forall m m' W,
  poison_cells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> poison_cells m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, A + n <= AIMG_HI -> disjoint_from W A n).
  { intros A n HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold poison_cells, AIMG_HI in *.
  destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

(* [comment removed for export] *)
Definition poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (addr size v lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (shad addr) [CB (Z.to_nat (shlen size)) (repeat (Z_to_bv 8 v) (Z.to_nat (shlen size)))].

End CANSEC1.
Local Ltac poison_tail sp v MU WM DST RSH FR ST :=
  do 3 step; do 8 step; step;
  eapply evtF_mono;
  [ eapply memset_spec;
    [ rewrite !unsigned_lit by (unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia); exact DST
    | assumption
    | rewrite !unsigned_lit by (unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia); exact RSH ]
  | ];
  let ms' := fresh "ms'" in let PO := fresh "PO" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
  let MI2 := fresh "MI2" in let DST2 := fresh "DST2" in let FR' := fresh "FR'" in let ST' := fresh "ST'" in
  intros ms' PO; unfold memset_post in PO; unfold poison_post; destruct_exs PO;
  destruct PO as (-> & MU2 & WM2 & MI2 & DST2);
  rewrite !unsigned_lit in MU2, DST2 by (unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia);
  rewrite ?unsigned_lit in DST2 by lia; rewrite ?(Z.mod_small v 256) in DST2 by lia; change (0 mod 256) with 0 in DST2;
  do 16 eexists; split; [reflexivity|];
  split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU2]; let xq := fresh in let Hxq := fresh in intros xq Hxq; cbn in Hxq |- *; tauto |];
  split; [eapply wmono_trans; [exact WM| exact WM2] |]; split; [exact MI2|];
  split; [| exact DST2];
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR';
  pose proof (stk_transport_disjoint bsegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST';
  eapply stk_release in FR'; [| exact ST' | lia]; cbn [cells_size csize Nat.add] in FR';
  match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end; exact FR'.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma poison_core : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m m1 : amem) (addr size v lo : Z) (junk fj : list byte),
  stk bsegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m1 ->
  poison_cells m1 ->
  rw_cells bsegs m1 (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m1 -> wmono bsegs m m1 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 0xffffffffffffffff) ->
  rw_cells bsegs m1 (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF bsegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 v) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52fa8) fc None m1 (seg_rom bsegs)).
Proof.
  intros until fj. intros ST CEIL LO MI PC FR MU WM AL SL SZ HI HE V V0 DST RIMG RSTK RSH.
  atop_facts. destruct PC as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR).
  unfold ablk, AIMG_HI, KLS in HI.                     (* [comment removed for export] *)
  assert (SHR : 0x800b6c00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "02S0?11801259171.10011801259171.91 11801259171.92 11801259171.99 12367362435.80 12367362435.81 12367362435.88 12367362435.89 17776320417.89 17776320417.90 17776320430.80 17776320430.81 19618399904.85 19618399904.93 21918414723.81 21918414723.82 21918414723.90 21918414723.91 24982578106.70 24982578106.75 24982578737.68 25878270240.90 25878270240.91 25878270254.80 25878270254.81 26072764852.79 26072764853.78 26072764854.77 26074863037.71 26074863037.76 26082619953.78 26082619966.89 28913119922.80 29429928528.10029429928528.91 29429928528.92 29429928528.99 29442626420.72 29442626420.80 29782367974.66 29784412410.73 29784412410.81 29784412664.72 29784412664.80 29784417117.68 29784418006.70 29784418006.75 29784418133.71 29786514268.79 29788590300.10029788590300.91 29788590300.92 29788590300.99 29794353372.85 29794353372.93 36115622433.89 36115622433.90 36115622446.80 36115622446.81 36423573305.10136423573305.10236423573305.93 36423573305.94 36993589379.81 36993589379.82 36993589379.90 36993589379.91 37728604022.79 37728604022.80 37728604022.88 37728604022.89 38793307797.79 38795403932.71 3945979267.80  3945979267.81  3945979267.87  3945979267.88  41356693149.66 41809558659.79 41809558659.80 41809558659.89 41809558659.90 42501437472.85 42501437472.93 42501437473.84 42501437479.94 42503534624.71 42511603750.71 42511603879.70 42511604004.73 42511604133.72 42511604512.69 42511605419.74 42548302974.10042548302974.91 42548302974.92 42548302974.99 42560672856.73 42560672856.81 42560673114.72 42560673114.80 43060403331.81 43060403331.82 43060403331.91 43060403331.92 43987951392.90 43987951392.91 43987951406.80 43987951406.81 44483185911.10044483185911.10144483185911.92 44483185911.93 44952393417.10044952393417.91 44952393417.92 44952393417.99 49343888933.10149343888933.10249343888933.93 49343888933.94 51481786499.81 51481786499.82 51481786499.91 51481786499.92 52076332701.79 53767577772.86 53767577772.87 53767577775.79 53767577775.80 55750620234.73 55750620234.81 5639787148.73  5639787148.81  5639787406.72  5639787406.80  5652583082.100 5652583082.91  5652583082.92  5652583082.99  59308628566.70 59308628695.71 59308628820.72 59308628949.73 59308629082.74 59308629336.71 59308629336.76 59308632823.73 59308632823.81 59310725456.78 59310725457.79 59310725459.77 59588178610.80 61917199023.79 61917199023.80 61917199023.87 61917199023.88 63235321900.78 63235321900.79 63235321902.88 63235321902.89 65096534934.86 65098632080.77 00000?00N00]00l00m00n00o01001401801<01@01A01B01C01D01E01F01G01H01I01M01Q01U01Y01`01g01n02C02M02b02i02j02m03003303603903<03=03>03?03@03A03B03C03D03E03F03G03H03I03J03K03L03P03T03X03\03`03d03h03l03m03n03o04004104204304404I04[04\04]04^04_05005105205305405=05D05M05T05b05i06306:06A06O06V06^06c06k07007807@07E07J07K07L07M07N07R07V07Z07^07j08608B08N08Q08T08W08Z08[08\08]08^08_08`08a08b08c08g08k08o09309809=09B09G09L09Q09V09[09`09e09o0:90:K0:R0:Y0:e0:o0;70;?0;G0;[0;c0;d0;h0;l0<00<40<80<<0<@0<D0<N0<ZS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRSSSSS2LOS2LOS2LOS2LOFFSSSSSSSS2LOS2LOS2LOS2LOS2HE2K9S2HE2K9S2HE2K9S2AL2SL2SZ2HI2HE1V2K2S2SZ2HE2K7S2AL2SL2SZ2HI2HE1V2K2S2HE2K9SS1VS1VS1VS1VS1VS1VSSSSSSSSSSSSSSSSS2LOS2LOS2LOS2LOS2LOS2LOS2LOS2LOSSSSSSSSS2AL2SL2HI1V1H2K93K12S2AL2SL2SZ2HI1V2K2SSSSS2AL2SL2SZ2HI1V1HSSSSS2HI1V2K2S2K22K3S2HI1V2K2S2K22K3S2SL2SZ2HI1V1HS2K22K3S2SZ2HE2K2S2K22K3S2K22K3S2SL2SZ2HI1V1HS2K22K3S3SHR2KTS3SHRS3SHR2KTS3SHRS3SHR2KTS3SHR2KTS3SHRS3SHRSSSSS2LOS2LOS2LOS2LOS4CEIL1H3SHRS4CEIL1H3SHRS4CEIL1H3SHRS4CEIL1H3SHRS1VS1VS1VS1VSSSSSSSSFS2LOS2LOS2LOS2LOS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS2SZ2HE2K3S2SZ2HE2K4S2SL2SZ2HI1V2K22K5S2K42K6S2K52K7S2HI1V2K22K9S2SZ2K72K9S3SHR2KTS3SHR2KTS2HE3K11S2AL2SL2SZ2K22K73K12S2HE3K10SS2LOS2LOS2LOS2LOS2LOS2LOS2LOS2LOS2SZ2HE2K7S2SZ2HI1V2K2".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  zstep. step. if_cases K1; zify_cond K1.               (* [comment removed for export] *)
  { exfalso. apply K1. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  do 3 step.                                           (* [comment removed for export] *)
  do 4 zstep.                                          (* [comment removed for export] *)
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  step. if_cases K2; zify_cond K2.                     (* [comment removed for export] *)
  2: do 6 step.                                        (* [comment removed for export] *)
  2: zstep; step; if_cases K3; zify_cond K3; [| exfalso; lia].   (* [comment removed for export] *)
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].           (* [comment removed for export] *)
  2: step; if_cases K5; zify_cond K5; [| exfalso; lia].          (* [comment removed for export] *)
  2: step; do 2 zstep.                                 (* [comment removed for export] *)
  2: step; if_cases K6; zify_cond K6; [exfalso; lia|].
  2: step; if_cases K7; zify_cond K7; [| exfalso; lia].          (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: zstep; step; if_cases K8; zify_cond K8;
       [ exfalso; apply K8; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; exact SL |].
  all: do 2 zstep.                                     (* [comment removed for export] *)
  all: step; if_cases K9; zify_cond K9.                (* [comment removed for export] *)
  all: try (exfalso; lia).
  (* [comment removed for export] *)
  2: do 6 step; zstep.                                 (* [comment removed for export] *)
  2: step; if_cases K10; zify_cond K10; [| exfalso; lia].
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K11; zify_cond K11; [exfalso; lia|].
  2: step; if_cases K12; zify_cond K12; [exfalso; lia|].
  (* [comment removed for export] *)
  all: do 3 step.                                      (* [comment removed for export] *)
  all: step; if_lit.                                   (* [comment removed for export] *)
  all: do 5 zstep.                                     (* [comment removed for export] *)
  all: replace ((Z.shiftr (addr + size + -8) 3 + 1) mod 18446744073709551616 - Z.shiftr addr 3) with (shlen size)
      by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  all: change (2147450880 + Z.shiftr addr 3) with (shad addr).
  (* [comment removed for export] *)
  all: step; if_cases KV; zify_cond KV;
      [| do 2 step; lstep; step; if_cases KT; zify_cond KT;
         [| exfalso; rewrite ?Z.mod_small in KT by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia); lia]].
  (* [comment removed for export] *)
  all: poison_tail sp v MU WM DST RSH FR ST.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma poison_shadow_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size v lo : Z) (junk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 0xffffffffffffffff) ->
  rw_cells bsegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF bsegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52f74) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC -> -> -> AL SL SZ HI HE V V0 DST RIMG RSTK RSH.
  atop_facts. pose proof PC as PC'. destruct PC' as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'.
  assert (SHR : 0x800b6c00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "01P0>1102156782.79 11912744615.7812367362435.7813021749692.7813219133678.7914159447534.781527479463.76 17646078182.6917776320431.7719007305966.7919049469500.781931560046.78 19447567726.7820633589486.7621918414723.7823026532974.7823446526574.7823814431342.7824630998586.7625071629079.7625071629079.7825071629079.7925314760359.7825878270255.7729442626420.7129786562375.6530862862062.7931081687356.7932595612014.7832651489978.7832825261550.7833039531175.7933155071726.7633486665994.7933680001082.7934056952330.7935281116398.7836115622446.7836993589379.7937107179452.7837390157038.763787933806.78 3945979267.78 40194010222.7840292163822.7941360887612.6541809558659.7641843714542.7843060403331.7943061431595.6743987951406.7844750652170.7844804625134.7945221239098.7845751589358.7946262085614.7846923716878.715012112366.78 50565006190.7851172767598.7951481786499.7853386120174.7853620364910.7953767577775.7755735955265.7156066145674.7856228262055.78563227834.78  57745675194.7858504403822.7858512233326.7858838550766.7659391397898.7659445487498.7859748865774.7660025031335.7961917199023.7763235321900.7563249165934.7863694018620.7963766009966.7863996031086.7864556005486.7864601217390.7665088762478.7865262970532.716630564334.79 6642473454.79 66761942666.786736605166.79 67800801447.7867943285742.787010956092.76 7260965451.71 8583720762.79 985337532.78  00000;00<00=00A00L00W00X00Y00]00h00l01701B01M01N01Y01d01o02402502602702802<02?02@02K02O02Z02_02j02k03603E03J03Y03d03h03i03m04804C04D04O04Z04l04m05805905=05A05P05[05`05k06606;06F06Q06\06]06h07307707807G07H07M07R07]07h08308B08Q08\08]08a08e09009409?09J09U09`09k09l0:70:B0:Q0:\0:]0:h0:l0;70;<0;@S4CEIL2LO1HSSS2HBS4CEIL2LO1HS4CEIL2LO1HSSS2LOS4CEIL2LO1HS2HBS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS3SPRSSSSS2LOS1VSS4CEIL2LO1HS2HBS4CEIL2LO1HS3SPRS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1H3SHRS3SPRS4CEIL2LO1H3SHRS4CEIL2LO1HS2LOSS2HBS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS2AL2SL2SZ1V1H3HI'SS4CEIL2LO1HSS2LOS2LOS4CEIL2LO1H3SHRS4CEIL2LO1HS3SPRS4CEIL2LO1HS4CEIL2LO1HS3SHRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS2LOFS4CEIL2LO1H3SHRSS3SPRS3SPRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRS4CEIL2LO1HSS2LOS2LOS4CEIL2LO1HS2HBS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1H3SHRS4CEIL2LO1HSS4CEIL2LO1HS2HBS4CEIL2LO1HS3SPRS2HB".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  word_range sp SPR.
  carve_frame 64%nat ST.
  do 8 step.                                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. if_cases KV; zify_cond KV.
  2: step; lstep; step; step; if_lit.                  (* [comment removed for export] *)
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         eapply (poison_core RNG ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mm addr size v lo junk) end.
  all: try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia.
  all: eapply poison_cells_frame; [exact PC | exact MU | exact WM | ].
  all: apply Forall_cons; [cbn; unfold AIMG_HI; lia|]; apply Forall_cons; [cbn; unfold AIMG_HI; lia | apply Forall_nil].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
