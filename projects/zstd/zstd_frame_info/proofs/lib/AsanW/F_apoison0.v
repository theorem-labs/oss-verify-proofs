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
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import F_apoison.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma poison_core0 : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m m1 : amem) (addr size v lo : Z) (junk fj : list byte),
  stk asegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m1 ->
  poison_cells m1 ->
  rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m1 -> wmono asegs m m1 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> ablk (addr - 8) (addr + size) -> addr + size < 2^47 ->     (* [comment removed for export] *)
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
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'.
  assert (SHR : 0x800b6c00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 <= shlen size).
  { unfold shad, shlen, ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "02S0?11801259171.10011801259171.10111801259171.92 11801259171.93 12367362435.81 12367362435.82 12367362435.89 12367362435.90 14684412918.80 14684412918.81 14684412918.89 14684412918.90 17776320417.90 17776320417.91 17776320430.81 17776320430.82 19618399904.86 19618399904.94 21918414723.82 21918414723.83 21918414723.91 21918414723.92 24982578106.71 24982578106.76 24982578737.69 25878270240.91 25878270240.92 25878270254.81 25878270254.82 26072764852.80 26072764853.79 26072764854.78 26074863037.72 26074863037.77 26082619953.79 26082619966.90 28913119922.81 29429928528.10029429928528.10129429928528.92 29429928528.93 29442626420.73 29442626420.81 29784412410.74 29784412410.82 29784412664.73 29784412664.81 29784417117.69 29784418006.71 29784418006.76 29784418133.72 29786514268.80 29786562375.67 29788590300.10029788590300.10129788590300.92 29788590300.93 29794353372.86 29794353372.94 36115622433.90 36115622433.91 36115622446.81 36115622446.82 36423573305.10236423573305.10336423573305.94 36423573305.95 36993589379.82 36993589379.83 36993589379.91 36993589379.92 38793307797.80 38795403932.72 3945979267.81  3945979267.82  3945979267.88  3945979267.89  41360887612.67 41809558659.80 41809558659.81 41809558659.90 41809558659.91 42501437472.86 42501437472.94 42501437473.85 42501437479.95 42503534624.72 42511603750.72 42511603879.71 42511604004.74 42511604133.73 42511604512.70 42511605419.75 42548302974.10042548302974.10142548302974.92 42548302974.93 42560672856.74 42560672856.82 42560673114.73 42560673114.81 43060403331.82 43060403331.83 43060403331.92 43060403331.93 43987951392.91 43987951392.92 43987951406.81 43987951406.82 44483185911.10144483185911.10244483185911.93 44483185911.94 44952393417.10044952393417.10144952393417.92 44952393417.93 49343888933.10249343888933.10349343888933.94 49343888933.95 51481786499.82 51481786499.83 51481786499.92 51481786499.93 52076332701.80 53767577772.87 53767577772.88 53767577775.80 53767577775.81 55750620234.74 55750620234.82 5639787148.74  5639787148.82  5639787406.73  5639787406.81  5652583082.100 5652583082.101 5652583082.92  5652583082.93  59308628566.71 59308628695.72 59308628820.73 59308628949.74 59308629082.75 59308629336.72 59308629336.77 59308632823.74 59308632823.82 59310725456.79 59310725457.80 59310725459.78 59588178610.81 61917199023.80 61917199023.81 61917199023.88 61917199023.89 63235321900.79 63235321900.80 63235321902.89 63235321902.90 65096534934.87 65098632080.78 00000?00N00]00l00m00n00o01001101201301401801<01@01D01E01F01G01H01I01J01K01L01M01Q01U01Y01]01d01k02202H02R02h02o03003303603903<03?03B03C03D03E03F03G03H03I03J03K03L03M03N03O03P03Q03R03V03Z03^03b03f03j03n04204304404504604L04_04`04a04b04c05505605705805905F05M05Z05a05m06406>06E06L06X06_06d06l07107907A07I07N07S07T07U07V07W07[07_07c07g08308?08K08W08Z08]08`08c08d08e08f08g08h08i08j08k08l09009409809<09A09F09K09P09U09Z09_09d09i09n0:80:B0:R0:Y0:`0;00;:0;B0;J0;R0;i0<10<20<60<:0<>0<B0<F0<J0<N0<R0<\0<iS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRSSSSSSSSS2LOS2LOS2LOS2LOFFSSSSSSSS2LOS2LOS2LOS2LOS2HE2K9S2HE2K9S2HE2K9S2AL2SL2SZ2HE1V3HI'2K2S2SZ2HE2K7S2AL2SL2SZ2HE1V3HI'2K2S2HE2K9SS1VS1VS1VS1VS1VS1VSSSSSSSSSSSSSSSSS2LOS2LOS2LOS2LOS2LOS2LOS2LOS2LOSSSSS2AL2SL1V1H3HI'2K93K12S2AL2SL2SZ1V3HI'2K2SSSSS2AL2SL2SZ1V1H3HI'SSSSS2SZ1V3HI'2K2S2K22K3S2SZ1V3HI'2K2S2K22K3S2SZ1V1H3HI'S2K22K3S2SZ2HE2K2S2K22K3S2K22K3S2SZ1V1H3HI'S2K22K3S3SHRS3SHR2KTS3SHRS3SHR2KTS3SHR2KTS3SHR2KTS3SHRS3SHRSSSSS2LOS2LOS2LOS2LOS4CEIL1H3SHRS4CEIL1H3SHRS4CEIL1H3SHRS4CEIL1H3SHRS1VS1VS1VS1VSSSSSSSSFS2LOS2LOS2LOS2LOS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS3SHRS2SZ2HE2K3S2SZ2HE2K4S2SZ1V3HI'2K22K5S2K42K6S2K52K7S2SZ1V3HI'2K22K9S2SZ2K72K9S3SHR2KTS3SHR2KTS2HE3K11S2AL2SL2SZ1V3HI'2K93K12S2HE3K10SS2LOS2LOS2LOS2LOS2LOS2LOS2LOS2LOS2SZ2HE2K7S2SZ1V3HI'2K2".
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

#[using="Type"] Lemma poison_shadow_spec0 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size v lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> ablk (addr - 8) (addr + size) -> addr + size < 2^47 ->     (* [comment removed for export] *)
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
  assert (SHR : 0x800b6c00 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 <= shlen size).
  { unfold shad, shlen, ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "01W0>100583406.79  11912744615.7812367362435.7813021749692.781340665966.78 1527479463.76 15629760750.7917646078182.6917776320431.7719049469500.782027029998.78 20313996398.7821918414723.7823893911790.7624630998586.7625071629079.7625071629079.7825071629079.7925240764910.7925259836654.7625314760359.7825878270255.7727453056622.7829442626420.7129514832494.7829786562375.6530410309102.7831081687356.7932377744366.7832651489978.7833039531175.7933486665994.7933680001082.7934056952330.7934255743086.7834874897390.7935010564462.7835052264302.7836115622446.7836993589379.7937107179452.7837774863470.7837881405678.7939219183342.763945979267.78 41360887612.6541809558659.764211417582.79 43060403331.7943061431595.674359095406.78 43987951406.7844750652170.784495156590.78 45221239098.7845295877870.7646356275438.7946388204398.7846923716878.7147219577582.7947407242478.7848757815150.7950693720814.7951106262638.7851481786499.7853767577775.7755735955265.7155810868206.7856064834414.7856066145674.7856228262055.78563227834.78  57745675194.7857839090926.7658388211694.7859391397898.7659445487498.7860025031335.7960366604398.7861674577390.7861917199023.7762233662062.7863235321900.7563694018620.7964635471598.7965262970532.7165529023470.7865752782446.7966761942666.7867503714926.7867800801447.7868705475182.786896978414.78 7010956092.76 7260965451.71 7400583278.78 8014158190.76 8492783342.76 8583720762.79 9053231598.79 9155751918.79 9333008750.78 985337532.78  00000;00<00=00A00L00M00X00Y00]00a00l01701801C01H01I01J01K01V01a01b01f02102402?02@02K02O02Z02_02`02o03403C03N03Y03d03o04304404804C04N04Y04Z04l04m05805905=05H05L05[05f05k06606A06L06Q06\06g07207=07H07I07M07N07Y07d08308408908>08I08T08c09209309>09I09M09X09\09`09k09l0:70:B0:Q0:\0:]0:h0;30;70;B0;M0;X0;c0;h0<30<>0<I0<MS4CEIL2LO1HSSS2HBS4CEIL2LO1HSS4CEIL2LO1HSS2LOS2HBS4CEIL2LO1HS4CEIL2LO1HSS4CEIL2LO1HS3SPRSSSS4CEIL2LO1HS4CEIL2LO1HSS2LOS4CEIL2LO1HS1VS4CEIL2LO1HSS4CEIL2LO1HS2HBS4CEIL2LO1HS3SPRSS4CEIL2LO1H3SHRS3SPRS4CEIL2LO1H3SHRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS2LOSS2HBS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSS2AL2SL2SZ1V1H3HI'SS4CEIL2LO1HSS2LOS4CEIL2LO1HS2LOS4CEIL2LO1H3SHRS4CEIL2LO1HS3SPRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS3SHRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HSS2LOFS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1H3SHRSS3SPRS3SPRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1H3SHRS4CEIL2LO1H3SHRSS4CEIL2LO1HS4CEIL2LO1HS2LOS4CEIL2LO1HS2LOS2HBS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1H3SHRS4CEIL2LO1HSS4CEIL2LO1HS4CEIL2LO1HS2HBS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS3SPRS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO1HS2HB".
rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  word_range sp SPR.
  carve_frame 64%nat ST.
  do 8 step.                                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. if_cases KV; zify_cond KV.
  2: step; lstep; step; step; if_lit.                  (* [comment removed for export] *)
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         eapply (poison_core0 RNG ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mm addr size v lo junk) end.
  all: try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia.
  all: eapply poison_cells_frame; [exact PC | exact MU | exact WM | ].
  all: apply Forall_cons; [cbn; unfold AIMG_HI; lia|]; apply Forall_cons; [cbn; unfold AIMG_HI; lia | apply Forall_nil].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition poison_post_k (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (addr k v lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + k)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (shad addr) [CB (Z.to_nat k) (repeat (Z_to_bv 8 v) (Z.to_nat k))].

#[using="Type"] Lemma poison_shadow_spec_k : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size k v lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 0xffffffffffffffff) -> shlen size = k ->
  rw_cells asegs m (shad addr) [CB (Z.to_nat k) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) k ->
  evtF asegs RNG (poison_post_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr k v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52f70) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC Ha0 Ha1 Ha2 AL SL SZ HI HE V V0 HK DST RIMG RSTK RSH. subst k.
  unfold poison_post_k. eapply poison_shadow_spec; eassumption.
Qed.

#[using="Type"] Lemma poison_shadow_spec0_k : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size k v lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> ablk (addr - 8) (addr + size) -> addr + size < 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 0xffffffffffffffff) -> shlen size = k ->
  rw_cells asegs m (shad addr) [CB (Z.to_nat k) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) k ->
  evtF asegs RNG (poison_post_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr k v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52f70) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC Ha0 Ha1 Ha2 AL SL SZ HI HE V V0 HK DST RIMG RSTK RSH. subst k.
  unfold poison_post_k. eapply poison_shadow_spec0; eassumption.
Qed.
End CANSEC1.
