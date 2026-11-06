(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase F_memset.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition poison_entry := 0x52f70%Z.

(* [comment removed for export] *)
Definition poison_cells (m : amem) : Prop :=
     rw_cells asegs m 0x98e28 [C8 (Z_to_bv 64 0x1329a8); C8 (Z_to_bv 64 0x9e678); C8 (Z_to_bv 64 0xa0e78);
                               C8 (Z_to_bv 64 0xa1b68); C8 (Z_to_bv 64 0xa1b70); C8 (Z_to_bv 64 0xa1b60)]
  /\ rw_cells asegs m 0x98e58 [C8 (Z_to_bv 64 0x9acc0)]
  /\ rw_cells asegs m 0x9acb8 [C8 (Z_to_bv 64 0x92164); C8 (Z_to_bv 64 0x92568)]
  /\ rw_cells asegs m 0xa0e78 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0xa1b60 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0xa06dc [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x132a20 [C8 (Z_to_bv 64 0xffffffffffffffff)].

#[using="Type"] Lemma poison_cells_frame : forall m m' W,
  poison_cells m -> munch W m m' -> wmono asegs m m' ->
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
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (shad addr) [CB (Z.to_nat (shlen size)) (repeat (Z_to_bv 8 v) (Z.to_nat (shlen size)))].

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
  pose proof (rw_cells_transport asegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR';
  pose proof (stk_transport_disjoint asegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST';
  eapply stk_release in FR'; [| exact ST' | lia]; cbn [cells_size csize Nat.add] in FR';
  match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end; exact FR'.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma poison_core : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m m1 : amem) (addr size v lo : Z) (junk fj : list byte),
  stk asegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m1 ->
  poison_cells m1 ->
  rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m1 -> wmono asegs m m1 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 0xffffffffffffffff) ->
  rw_cells asegs m1 (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF asegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 v) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52fa4) fc None m1 (seg_rom asegs)).
Proof.
  intros until fj. intros ST CEIL LO MI PC FR MU WM AL SL SZ HI HE V V0 DST RIMG RSTK RSH.
  atop_facts. destruct PC as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR).
  unfold ablk, AIMG_HI, KLS in HI.                     (* [comment removed for export] *)
  assert (SHR : 0x800b6c00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "02S0?11801259171.10011801259171.91 11801259171.92 11801259171.99 12367362435.80 12367362435.81 12367362435.88 12367362435.89 14684412918.79 14684412918.80 14684412918.88 14684412918.89 17776320417.89 17776320417.90 17776320430.80 17776320430.81 19618399904.85 19618399904.93 21918414723.81 21918414723.82 21918414723.90 21918414723.91 24982578106.70 24982578106.75 24982578737.68 25878270240.90 25878270240.91 25878270254.80 25878270254.81 26072764852.79 26072764853.78 26072764854.77 26074863037.71 26074863037.76 26082619953.78 26082619966.89 28913119922.80 29429928528.10029429928528.91 29429928528.92 29429928528.99 29442626420.72 29442626420.80 29782367974.66 29784412410.73 29784412410.81 29784412664.72 29784412664.80 29784417117.68 29784418006.70 29784418006.75 29784418133.71 29786514268.79 29788590300.10029788590300.91 29788590300.92 29788590300.99 29794353372.85 29794353372.93 36115622433.89 36115622433.90 36115622446.80 36115622446.81 36423573305.10136423573305.10236423573305.93 36423573305.94 36993589379.81 36993589379.82 36993589379.90 36993589379.91 38793307797.79 38795403932.71 3945979267.80  3945979267.81  3945979267.87  3945979267.88  41356693149.66 41809558659.79 41809558659.80 41809558659.89 41809558659.90 42501437472.85 42501437472.93 42501437473.84 42501437479.94 42503534624.71 42511603750.71 42511603879.70 42511604004.73 42511604133.72 42511604512.69 42511605419.74 42548302974.10042548302974.91 42548302974.92 42548302974.99 42560672856.73 42560672856.81 42560673114.72 42560673114.80 43060403331.81 43060403331.82 43060403331.91 43060403331.92 43987951392.90 43987951392.91 43987951406.80 43987951406.81 44483185911.10044483185911.10144483185911.92 44483185911.93 44952393417.10044952393417.91 44952393417.92 44952393417.99 49343888933.10149343888933.10249343888933.93 49343888933.94 51481786499.81 51481786499.82 51481786499.91 51481786499.92 52076332701.79 53767577772.86 53767577772.87 53767577775.79 53767577775.80 55750620234.73 55750620234.81 5639787148.73  5639787148.81  5639787406.72  5639787406.80  5652583082.100 5652583082.91  5652583082.92  5652583082.99  59308628566.70 59308628695.71 59308628820.72 59308628949.73 59308629082.74 59308629336.71 59308629336.76 59308632823.73 59308632823.81 59310725456.78 59310725457.79 59310725459.77 59588178610.80 61917199023.79 61917199023.80 61917199023.87 61917199023.88 63235321900.78 63235321900.79 63235321902.88 63235321902.89 65096534934.86 65098632080.77 00000?00N00]00l00m00n00o01001101201301401801<01@01D01E01F01G01H01I01J01K01L01M01Q01U01Y01]01d01k02202G02Q02f02m02n03103403703:03=03@03A03B03C03D03E03F03G03H03I03J03K03L03M03N03O03P03T03X03\03`03d03h03l04004104204304404I04[04\04]04^04_05005105205305405=05D05M05T05b05i06306:06A06O06V06^06c06k07007807@07E07J07K07L07M07N07R07V07Z07^07j08608B08N08Q08T08W08Z08[08\08]08^08_08`08a08b08c08g08k08o09309809=09B09G09L09Q09V09[09`09e09o0:90:K0:R0:Y0:e0:o0;70;?0;G0;[0;c0;d0;h0;l0<00<40<80<<0<@0<D0<N0<ZS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRSSSSSSSSS2LOS2LOS2LOS2LOFFSSSSSSSS2LOS2LOS2LOS2LOS2HE2K9S2HE2K9S2HE2K9S2AL2SL2SZ2HI2HE1V2K2S2SZ2HE2K7S2AL2SL2SZ2HI2HE1V2K2S2HE2K9SS1VS1VS1VS1VS1VS1VSSSSSSSSSSSSSSSSS2LOS2LOS2LOS2LOS2LOS2LOS2LOS2LOSSSSS2AL2SL2HI1V1H2K93K12S2AL2SL2SZ2HI1V2K2SSSSS2AL2SL2SZ2HI1V1HSSSSS2HI1V2K2S2K22K3S2HI1V2K2S2K22K3S2SL2SZ2HI1V1HS2K22K3S2SZ2HE2K2S2K22K3S2K22K3S2SL2SZ2HI1V1HS2K22K3S3SHR2KTS3SHRS3SHR2KTS3SHRS3SHR2KTS3SHR2KTS3SHRS3SHRSSSSS2LOS2LOS2LOS2LOS4CEIL1H3SHRS4CEIL1H3SHRS4CEIL1H3SHRS4CEIL1H3SHRS1VS1VS1VS1VSSSSSSSSFS2LOS2LOS2LOS2LOS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS2SZ2HE2K3S2SZ2HE2K4S2SL2SZ2HI1V2K22K5S2K42K6S2K52K7S2HI1V2K22K9S2SZ2K72K9S3SHR2KTS3SHR2KTS2HE3K11S2AL2SL2SZ2K22K73K12S2HE3K10SS2LOS2LOS2LOS2LOS2LOS2LOS2LOS2LOS2SZ2HE2K7S2SZ2HI1V2K2".
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
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 0xffffffffffffffff) ->
  rw_cells asegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF asegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52f70) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC -> -> -> AL SL SZ HI HE V V0 DST RIMG RSTK RSH.
  atop_facts. pose proof PC as PC'. destruct PC' as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'.
  assert (SHR : 0x800b6c00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "01W0>100583406.79  11912744615.7812367362435.7813021749692.781340665966.78 1527479463.76 15629760750.7917646078182.6917776320431.7719049469500.782027029998.78 20313996398.7821918414723.7823893911790.7624630998586.7625071629079.7625071629079.7825071629079.7925240764910.7925259836654.7625314760359.7825878270255.7727453056622.7829442626420.7129514832494.7829786562375.6530410309102.7831081687356.7932377744366.7832651489978.7833039531175.7933486665994.7933680001082.7934056952330.7934255743086.7834874897390.7935010564462.7835052264302.7836115622446.7836993589379.7937107179452.7837774863470.7837881405678.7939219183342.763945979267.78 41360887612.6541809558659.764211417582.79 43060403331.7943061431595.674359095406.78 43987951406.7844750652170.784495156590.78 45221239098.7845295877870.7646356275438.7946388204398.7846923716878.7147219577582.7947407242478.7848757815150.7950693720814.7951106262638.7851481786499.7853767577775.7755735955265.7155810868206.7856064834414.7856066145674.7856228262055.78563227834.78  57745675194.7857839090926.7658388211694.7859391397898.7659445487498.7860025031335.7960366604398.7861674577390.7861917199023.7762233662062.7863235321900.7563694018620.7964635471598.7965262970532.7165529023470.7865752782446.7966761942666.7867503714926.7867800801447.7868705475182.786896978414.78 7010956092.76 7260965451.71 7400583278.78 8014158190.76 8492783342.76 8583720762.79 9053231598.79 9155751918.79 9333008750.78 985337532.78  00000;00<00=00A00L00M00X00Y00]00a00l01701801C01H01I01J01K01V01a01b01f02102402?02@02K02O02Z02_02`02o03403C03N03Y03d03o04304404804C04N04Y04Z04l04m05805905=05H05L05[05f05k06606A06L06Q06\06g07207=07H07I07M07N07Y07d08308408908>08I08T08c09209309>09I09M09X09\09`09k09l0:70:B0:Q0:\0:]0:h0;30;70;B0;M0;X0;c0;h0<30<>0<I0<MS4CEIL2LO1HSSS2HBS4CEIL2LO1HSS4CEIL2LO1HSS2LOS2HBS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HS3SPRSSSS4CEIL2LO1HS4CEIL2LO1HSS2LOS4CEIL2LO1HS1VS4CEIL2LO1HSS4CEIL2LO1HS2HBS4CEIL2LO1HS3SPRSS4CEIL2LO1H3SHRS3SPRS4CEIL2LO1H3SHRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS2LOSS2HBS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSS2AL2SL2SZ1V1H3HI'SS4CEIL2LO1HSS2LOS4CEIL2LO1HS2LOS4CEIL2LO1H3SHRS4CEIL2LO1HS3SPRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS3SHRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSS2LOFS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1H3SHRSS3SPRS3SPRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRSS4CEIL2LO1HS4CEIL2LO1HS2LOS4CEIL2LO1HS2LOS2HBS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1H3SHRS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS2HBS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS3SPRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS2HB".
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
